import H0mework.NavierStokes.VelocityEndpoint.MacroPhysicalStageKineticClosure
import H0mework.NavierStokes.VelocityGalerkin.InitialConvergence

/-!
# The endpoint kinetic-energy atom of an actual macro stage

At one recursive endpoint macro edge, the old actual contact lineage has a
source-generated kinetic-mass limit, while the same edge writes a literal
physical velocity at its internal accumulation point.  Their square-mass
difference is the endpoint kinetic-energy atom.

This module proves that the atom is exactly the already generated kinetic
endpoint defect.  It then identifies the atom as the limiting square mass of
both the aligned whole-carrier residual and the kinetic coordinate of the
native macro trace.  Finally, the exact finite Galerkin kinetic/viscous
identity is transported to the same scale: its limiting gap from the old
actual contact mass is precisely this atom.

No endpoint, defect value, cutoff, convergence witness, energy equality or
branch is supplied by a caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

open scoped ENNReal Interval

open Filter Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointComponentOccurrenceMacroWrite.WholeRestartEndpointComponentMacroPhase
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityProcess
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointAlignedResponsibilityMacroWrite
open AffineRelaxation

noncomputable section

private theorem wholeRestartWeakEndpointRow_tendsto
    (sequence : ℕ → WholeRestartVelocityEndpointState)
    (endpoint : WholeRestartVelocityEndpointState)
    (weakTendsto :
      ∀ test : WholeRestartVelocityEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop (nhds (inner ℂ endpoint test)))
    (wave : NonzeroIntegerWavevector) :
    Tendsto (fun index => sequence index wave) atTop
      (nhds (endpoint wave)) := by
  have functionTendsto :
      Tendsto
        (fun index => WithLp.ofLp (sequence index wave))
        atTop
        (nhds (WithLp.ofLp (endpoint wave))) := by
    exact tendsto_pi_nhds.mpr fun coordinate =>
      velocityWeakTendsto_coordinate
        sequence endpoint weakTendsto wave coordinate
  have lifted :=
    (PiLp.continuous_toLp
      (p := (2 : ENNReal))
      (β := fun _ : Coordinate => ℂ)).tendsto
        (WithLp.ofLp (endpoint wave))
      |>.comp functionTendsto
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using lifted

/-- On one actual contact, the physical velocity row and its weighted
vorticity kinetic row have exactly the same square norm. -/
theorem wholeRestartContactVelocityState_row_norm_sq_eq_kinetic
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (wave : NonzeroIntegerWavevector) :
    ‖wholeRestartContactVelocityState initial index wave‖ ^ 2 =
      ‖wholeRestartContactKineticState initial index wave‖ ^ 2 := by
  let state := (run initial index).contact.physicalState
  change
    ‖puncturedWholeVelocityEuclideanCoefficient state wave‖ ^ 2 =
      ‖puncturedWholeVorticityKineticEuclideanCoefficient state wave‖ ^ 2
  rw [puncturedWholeVelocityEuclideanCoefficient_norm_sq
      state (run initial index).contact.transverse wave,
    puncturedWholeVorticityKineticEuclideanCoefficient_norm_sq]

/-- The two weak endpoints selected on the same actual contact lineage have
equal complete square mass.  The equality is forced rowwise before summing
the whole `lp²` carrier; it does not assume strong endpoint convergence. -/
theorem wholeRestartVelocityWeakEndpoint_norm_sq_eq_kineticEndpoint
    {ν : Viscosity}
    {initial : GeneratedWholeRestartCurrent ν}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (receipt :
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
        initial elapsedBounded) :
    ‖receipt.velocityEndpoint‖ ^ 2 =
      ‖receipt.kineticReceipt.endpoint‖ ^ 2 := by
  have rowNormSqEq (wave : NonzeroIntegerWavevector) :
      ‖receipt.velocityEndpoint wave‖ ^ 2 =
        ‖receipt.kineticReceipt.endpoint wave‖ ^ 2 := by
    let selected := receipt.subsequence
    have velocityRowTendsto :
        Tendsto
          (fun index =>
            wholeRestartContactVelocityState
              initial (selected index) wave)
          atTop (nhds (receipt.velocityEndpoint wave)) :=
      wholeRestartWeakEndpointRow_tendsto
        (fun index =>
          wholeRestartContactVelocityState initial (selected index))
        receipt.velocityEndpoint receipt.velocity_weak_tendsto_shared wave
    have kineticWeakTendstoShared :
        ∀ test : WholeRestartKineticEndpointState,
          Tendsto
            (fun index =>
              inner ℂ
                (wholeRestartContactKineticState
                  initial (selected index)) test)
            atTop
            (nhds (inner ℂ receipt.kineticReceipt.endpoint test)) := by
      intro test
      simpa only [selected,
        GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
        Function.comp_def] using
        (receipt.kineticReceipt.weak_tendsto test).comp
          receipt.velocitySubsubsequence_strictMono.tendsto_atTop
    have kineticRowTendsto :
        Tendsto
          (fun index =>
            wholeRestartContactKineticState
              initial (selected index) wave)
          atTop (nhds (receipt.kineticReceipt.endpoint wave)) :=
      wholeRestartWeakEndpointRow_tendsto
        (fun index =>
          wholeRestartContactKineticState initial (selected index))
        receipt.kineticReceipt.endpoint kineticWeakTendstoShared wave
    have velocitySquareTendsto := velocityRowTendsto.norm.pow 2
    have kineticSquareTendsto := kineticRowTendsto.norm.pow 2
    have sameSequence :
        (fun index =>
          ‖wholeRestartContactVelocityState
              initial (selected index) wave‖ ^ 2) =
        (fun index =>
          ‖wholeRestartContactKineticState
              initial (selected index) wave‖ ^ 2) := by
      funext index
      exact wholeRestartContactVelocityState_row_norm_sq_eq_kinetic
        initial (selected index) wave
    rw [sameSequence] at velocitySquareTendsto
    exact tendsto_nhds_unique velocitySquareTendsto kineticSquareTendsto
  rw [show
      ‖receipt.velocityEndpoint‖ ^ 2 =
        ∑' wave : NonzeroIntegerWavevector,
          ‖receipt.velocityEndpoint wave‖ ^ 2 by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.norm_rpow_eq_tsum
            (p := (2 : ℝ≥0∞)) (by norm_num)
            receipt.velocityEndpoint),
    show
      ‖receipt.kineticReceipt.endpoint‖ ^ 2 =
        ∑' wave : NonzeroIntegerWavevector,
          ‖receipt.kineticReceipt.endpoint wave‖ ^ 2 by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          (lp.norm_rpow_eq_tsum
            (p := (2 : ℝ≥0∞)) (by norm_num)
            receipt.kineticReceipt.endpoint)]
  exact tsum_congr rowNormSqEq

namespace GeneratedWholeRestartEndpointMacroStep

/-- The kinetic square mass lost between the old actual contact limit and
the physical value written at this macro stage's accumulation interface. -/
def physicalStageKineticEnergyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) : ℝ :=
  wholeRestartKineticMassLimit current -
    ‖step.physicalStage step.physicalStageAccumulation‖ ^ 2

/-- The actual-stage kinetic-energy atom is exactly the source-generated
weak-endpoint defect. -/
theorem physicalStageKineticEnergyAtom_eq_defect
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    step.physicalStageKineticEnergyAtom =
      wholeRestartKineticWeakEndpointDefect current
        (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
          current step.elapsedBounded).family.endpointReceipt.kineticReceipt.endpoint := by
  let receipt :=
    (generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded).family.endpointReceipt
  rw [physicalStageKineticEnergyAtom, step.physicalStage_accumulation,
    wholeRestartVelocityWeakEndpoint_norm_sq_eq_kineticEndpoint receipt]
  rfl

/-- The complete aligned kinetic residual reads the same endpoint atom as
its exact limiting square mass. -/
theorem alignedKineticResidual_norm_sq_tendsto_energyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Tendsto
      (fun index =>
        ‖wholeRestartEndpointAlignedKineticResidual
          current step.elapsedBounded index‖ ^ 2)
      atTop (nhds step.physicalStageKineticEnergyAtom) := by
  rw [step.physicalStageKineticEnergyAtom_eq_defect]
  exact
    wholeRestartEndpointAlignedKineticResidual_norm_sq_tendsto_defect
      step.elapsedBounded

/-- The kinetic coordinate of the native macro trace reads exactly the same
endpoint atom before any finite Fourier observation. -/
theorem alignedMacroKineticTrace_norm_sq_tendsto_energyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    Tendsto
      (fun index =>
        ‖(linearResidualTrace wholeRestartEndpointAlignedMacroKeep
          (wholeRestartEndpointAlignedMacroPending
            current step.elapsedBounded accumulationRead) index).2‖ ^ 2)
      atTop (nhds step.physicalStageKineticEnergyAtom) := by
  rw [step.physicalStageKineticEnergyAtom_eq_defect]
  exact
    wholeRestartEndpointAlignedMacro_kineticTrace_norm_sq_tendsto_defect
      step.elapsedBounded

/-- After multiplying the finite Galerkin kinetic convention by two, the
limit gap between the old actual contact mass and every exact terminal-plus-
viscous balance is precisely the endpoint kinetic-energy atom. -/
theorem contactMass_sub_galerkinExactBalance_tendsto_energyAtom
    {ν : Viscosity}
    {current next : GeneratedWholeRestartCurrent ν}
    (step : GeneratedWholeRestartEndpointMacroStep ν current next) :
    let ledger :=
      generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
        current step.elapsedBounded
    let receipt := ledger.family.endpointReceipt
    Tendsto
      (fun index =>
        wholeRestartContactKineticMass current (receipt.subsequence index) -
          2 *
            (finiteStateVorticityKineticEnergy
                (wholeRestartModes index)
                ((ledger.family.stage index).trajectory 1) +
              ν.coeff *
                (∫ actual in (0 : ℝ)..1,
                  finiteStateVorticityMass
                    (wholeRestartModes index)
                    ((ledger.family.stage index).trajectory actual))))
      atTop (nhds step.physicalStageKineticEnergyAtom) := by
  dsimp only
  let ledger :=
    generatedWholeRestartVelocityEndpointUniformKineticViscousLedger
      current step.elapsedBounded
  let receipt := ledger.family.endpointReceipt
  have massTendsto :
      Tendsto
        (fun index =>
          wholeRestartContactKineticMass current
            (receipt.subsequence index))
        atTop (nhds (wholeRestartKineticMassLimit current)) := by
    simpa only [receipt,
      GeneratedWholeRestartVelocityWeakEndpointAtAccumulation.subsequence,
      Function.comp_def] using
      receipt.kineticReceipt.mass_tendsto.comp
        receipt.velocitySubsubsequence_strictMono.tendsto_atTop
  have initialEnergyTendsto :=
    wholeRestartVelocityEndpointGalerkinInitialKineticEnergy_tendsto
      receipt.velocityEndpoint receipt.velocityEndpoint_transverse
  have doubledInitialEnergyTendsto :
      Tendsto
        (fun index =>
          2 * finiteStateVorticityKineticEnergy
            (wholeRestartModes index)
            (wholeRestartVelocityEndpointFiniteVorticityInitialState
              index receipt.velocityEndpoint))
        atTop (nhds (‖receipt.velocityEndpoint‖ ^ 2)) := by
    have twoTendsto :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    convert twoTendsto.mul initialEnergyTendsto using 1
    congr 1
    ring
  have gapTendsto := massTendsto.sub doubledInitialEnergyTendsto
  rw [step.physicalStageKineticEnergyAtom_eq_defect]
  convert gapTendsto using 1
  · funext index
    change
      wholeRestartContactKineticMass current
            (receipt.subsequence index) -
          2 *
            (finiteStateVorticityKineticEnergy
                (wholeRestartModes index)
                ((ledger.family.stage index).trajectory 1) +
              ν.coeff *
                (∫ actual in (0 : ℝ)..1,
                  finiteStateVorticityMass
                    (wholeRestartModes index)
                    ((ledger.family.stage index).trajectory actual))) =
        wholeRestartContactKineticMass current
            (receipt.subsequence index) -
          2 * finiteStateVorticityKineticEnergy
            (wholeRestartModes index)
            (wholeRestartVelocityEndpointFiniteVorticityInitialState
              index receipt.velocityEndpoint)
    have balance := ledger.exact_balance index
      (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)
    rw [(ledger.family.stage index).initial] at balance
    rw [balance]
  · rw [wholeRestartVelocityWeakEndpoint_norm_sq_eq_kineticEndpoint receipt]
    rfl

end GeneratedWholeRestartEndpointMacroStep

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
end NavierStokes
end SaturationMonoid
