import H0mework.NavierStokes.SourceReadout.Action
import H0mework.NavierStokes.Restart.NativeAccumulationRoot
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Complete source stress on the original cofinal subsequence

The existing cofinal receipt fixes the kinetic and velocity endpoints.
Compactness refines its own subsequence to retain all stress coordinates
and their nonlinear/pressure actions together. No stress equality with the
weak velocity endpoint or new root authority is asserted.
-/

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.NativeCofinalStress

open scoped BigOperators
open Filter Set Metric
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeStressSource NativeStressCurlAlgebra

noncomputable section

/-- The complete flux at the original generated contact. -/
def contactStress {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (stage : ℕ) : NativeFluidStressFourierState :=
  quadraticFlux (wholeBiotSavartVelocityState (run initial stage).contact.physicalState)

theorem contactStress_norm_le {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu)
    (stage : ℕ) (wave : IntegerWavevector) (output input : Coordinate) :
    ‖contactStress initial stage wave output input‖ ≤
      ‖wholeRestartContactVelocityState initial 0‖ ^ 2 := by
  have bound := quadraticFlux_biotSavart_norm_le (run initial stage).contact.physicalState
    (run initial stage).contact.transverse wave output input
  rw [← wholeRestartContactVelocityState_norm_sq initial stage] at bound
  exact bound.trans ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (wholeRestartContactVelocityState_norm_le_initial initial stage))

/-- A refinement of the fixed cofinal receipt carries the entire stress simultaneously. -/
structure CofinalStressAt {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) where
  refinement : ℕ → ℕ
  refinement_strictMono : StrictMono refinement
  stress : NativeFluidStressFourierState
  stress_norm_le : ∀ wave output input, ‖stress wave output input‖ ≤
    ‖wholeRestartContactVelocityState initial 0‖ ^ 2
  stress_tendsto : Tendsto
    (fun index => contactStress initial
      ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).subsequence
        (refinement index))) atTop (nhds stress)

/-- Compactness refines the original cofinal subsequence, with its source budget already fixed. -/
def sourceGeneratedCofinalStress {nu : Viscosity} (initial : GeneratedWholeRestartCurrent nu) :
    CofinalStressAt initial := Classical.choice <| by
  let radius := ‖wholeRestartContactVelocityState initial 0‖ ^ 2
  let ball : Set NativeFluidStressFourierState := Set.pi Set.univ fun _ =>
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) radius
  have compact : IsCompact ball :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let sequence : ℕ → NativeFluidStressFourierState := fun index =>
    contactStress initial
      ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).subsequence index)
  have sequenceMem : ∀ index, sequence index ∈ ball := by
    intro index wave _ output _ input _
    change dist _ 0 ≤ radius
    simpa only [dist_zero_right] using contactStress_norm_le initial _ wave output input
  obtain ⟨stress, stressMem, refinement, strictMono, convergence⟩ :=
    compact.tendsto_subseq sequenceMem
  exact ⟨{
    refinement := refinement
    refinement_strictMono := strictMono
    stress := stress
    stress_norm_le := fun wave output input => by
      have bound := stressMem wave (by trivial : wave ∈ Set.univ)
        output (by trivial : output ∈ Set.univ) input (by trivial : input ∈ Set.univ)
      simpa only [Metric.mem_closedBall, dist_zero_right] using bound
    stress_tendsto := convergence }⟩

/-- The source pressure contraction is the same continuous complex-linear readout. -/
def stressPressureCLM (wave : IntegerWavevector) : NativeFluidStressCoefficient →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := stressPressureCoefficient wave
      map_add' := by
        intro left right
        by_cases zero : wave = 0
        · simp [stressPressureCoefficient, zero]
        · simp [stressPressureCoefficient, zero, dotProduct, Fin.sum_univ_succ]
          ring
      map_smul' := by
        intro scalar tensor
        by_cases zero : wave = 0
        · simp [stressPressureCoefficient, zero]
        · simp [stressPressureCoefficient, zero, dotProduct, Fin.sum_univ_succ]
          ring }

@[simp] theorem stressPressureCLM_apply (wave : IntegerWavevector)
    (tensor : NativeFluidStressCoefficient) :
    stressPressureCLM wave tensor = stressPressureCoefficient wave tensor := rfl

namespace CofinalStressAt

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

def stage (receipt : CofinalStressAt initial) (index : ℕ) : ℕ :=
  (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).subsequence
    (receipt.refinement index)

theorem stage_strictMono (receipt : CofinalStressAt initial) : StrictMono receipt.stage :=
  (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).subsequence_strictMono.comp
    receipt.refinement_strictMono

/-- The kinetic endpoint is literally the original receipt's endpoint. -/
theorem kineticWeak_tendsto (receipt : CofinalStressAt initial)
    (test : WholeRestartKineticEndpointState) :
    Tendsto (fun index => inner ℂ (wholeRestartContactKineticState initial (receipt.stage index)) test)
      atTop (nhds (inner ℂ
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint test)) :=
  ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticWeak_tendsto test).comp
    receipt.refinement_strictMono.tendsto_atTop

/-- The physical velocity endpoint is retained on exactly the same refinement. -/
theorem velocityWeak_tendsto (receipt : CofinalStressAt initial)
    (test : WholeRestartVelocityEndpointState) :
    Tendsto (fun index => inner ℂ (wholeRestartContactVelocityState initial (receipt.stage index)) test)
      atTop (nhds (inner ℂ
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint test)) :=
  ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityWeak_tendsto test).comp
    receipt.refinement_strictMono.tendsto_atTop

theorem divergence_tendsto (receipt : CofinalStressAt initial) :
    Tendsto (fun index => nativeFluidStressDivergenceCoefficient
      (contactStress initial (receipt.stage index))) atTop
      (nhds (nativeFluidStressDivergenceCoefficient receipt.stress)) :=
  wholeStressDivergenceCLM.continuous.continuousAt.tendsto.comp receipt.stress_tendsto

theorem action_tendsto (receipt : CofinalStressAt initial) :
    Tendsto (fun index => nativeFluidConstitutiveVorticityAction
      (contactStress initial (receipt.stage index))) atTop
      (nhds (nativeFluidConstitutiveVorticityAction receipt.stress)) :=
  wholeStressActionCLM.continuous.continuousAt.tendsto.comp receipt.stress_tendsto

/-- The whole velocity nonlinearity is the divergence of the generated cofinal stress. -/
theorem velocityNonlinear_tendsto (receipt : CofinalStressAt initial) :
    Tendsto (fun index wave => wholeStateVelocityNonlinearCoefficientAt
      (wholeBiotSavartVelocityState (run initial (receipt.stage index)).contact.physicalState) wave)
      atTop (nhds (nativeFluidStressDivergenceCoefficient receipt.stress)) := by
  have convergence := receipt.divergence_tendsto
  have sourceEq : (fun index => nativeFluidStressDivergenceCoefficient
      (contactStress initial (receipt.stage index))) =
      (fun index wave => wholeStateVelocityNonlinearCoefficientAt
        (wholeBiotSavartVelocityState (run initial (receipt.stage index)).contact.physicalState) wave) := by
    funext index wave
    exact quadraticFlux_divergence _ (wholeBiotSavartVelocityState_transverse _) wave
  rwa [sourceEq] at convergence

/-- The original complete vorticity action has the same refined cofinal limit. -/
theorem vorticityNonlinear_tendsto (receipt : CofinalStressAt initial) :
    Tendsto (fun index wave => wholeStateVorticityNonlinearCoefficientAt
      (run initial (receipt.stage index)).contact.physicalState wave)
      atTop (nhds (nativeFluidConstitutiveVorticityAction receipt.stress)) := by
  have convergence := receipt.action_tendsto
  have sourceEq : (fun index => nativeFluidConstitutiveVorticityAction
      (contactStress initial (receipt.stage index))) =
      (fun index wave => wholeStateVorticityNonlinearCoefficientAt
        (run initial (receipt.stage index)).contact.physicalState wave) := by
    funext index wave
    exact quadraticFlux_biotSavart_action _
      (run initial (receipt.stage index)).contact.physicalState_zero
      (run initial (receipt.stage index)).contact.transverse wave
  rwa [sourceEq] at convergence

/-- Pressure is read from the same converging tensors, including its original zero mode. -/
theorem pressure_tendsto (receipt : CofinalStressAt initial) (wave : IntegerWavevector) :
    Tendsto (fun index => sourcePressure
      (run initial (receipt.stage index)).contact.physicalState wave) atTop
      (nhds (stressPressureCoefficient wave (receipt.stress wave))) := by
  have rowTendsto := tendsto_pi_nhds.mp receipt.stress_tendsto wave
  have pressureTendsto := ((stressPressureCLM wave).continuous.tendsto (receipt.stress wave)).comp
    rowTendsto
  simpa only [Function.comp_def, stressPressureCLM_apply, sourcePressure, contactStress, stage]
    using pressureTendsto

end CofinalStressAt

end
end SaturationMonoid.NavierStokes.NativeCofinalStress
